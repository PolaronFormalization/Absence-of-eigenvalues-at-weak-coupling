import Froehlich.Nodes.OP02DiagonalIdentity

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- Each term in the polarized formula is jointly continuous on the full form domain. -/
theorem polarizedThreshold_terms_continuous :
    Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      ⟪oneParticleRadialMap fh.1,
        thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap fh.2)⟫_ℂ) ∧
    Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) (translatedLinearSource g P fh.1)*
        translatedLinearSource g P fh.2) ∧
    Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      (starRingEnd ℂ) (translatedLinearSource g P fh.1)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap fh.2⟫_ℂ) ∧
    Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      ⟪oneParticleRadialMap fh.1,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ*
        translatedLinearSource g P fh.2) := by
  have hu : Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      oneParticleRadialMap fh.1) := oneParticleRadialMap.continuous.comp continuous_fst
  have hv : Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      oneParticleRadialMap fh.2) := oneParticleRadialMap.continuous.comp continuous_snd
  have hLf : Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      translatedLinearSource g P fh.1) := (translatedLinearSource g P).continuous.comp continuous_fst
  have hLh : Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      translatedLinearSource g P fh.2) := (translatedLinearSource g P).continuous.comp continuous_snd
  have hstar : Continuous (fun fh : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      (starRingEnd ℂ) (translatedLinearSource g P fh.1)) := hLf.star
  have hb : Continuous (fun _ : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      thresholdKernelSourceVector e he g hg hs P hP) := continuous_const
  have hc : Continuous (fun _ : OneParticleEnergySpace 0 × OneParticleEnergySpace 0 =>
      (kernelConstant e he g hg hs P : ℂ)) := continuous_const
  exact ⟨hu.inner (𝕜 := ℂ) ((thresholdBoundedOperator e he g hg hs CD hCD hquad P hP).continuous.comp hv),
    (hc.mul hstar).mul hLh,hstar.mul (hb.inner (𝕜 := ℂ) hv),(hu.inner (𝕜 := ℂ) hb).mul hLh⟩

end Froehlich
