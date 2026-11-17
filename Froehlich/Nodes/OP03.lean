import Froehlich.Nodes.OP03MixedIdentity
import Froehlich.Nodes.OP03Continuity
import Froehlich.Nodes.OP02

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-! OP03: direct mixed identity and joint continuity of each of its four terms. -/
def OP03FixedReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) : Prop :=
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f h : OneParticleEnergySpace 0),
    translatedThresholdForm e he g hquarter heLower hquadratic P hP f h =
      ⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap h)⟫_ℂ+
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) (translatedLinearSource g P f)*translatedLinearSource g P h+
      (starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap h⟫_ℂ+
      ⟪oneParticleRadialMap f,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ*translatedLinearSource g P h) ∧
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
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
        translatedLinearSource g P fh.2)

theorem finalOP03_reference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    OP03FixedReference e he g hg hs CD hCD hquad hquarter heLower hquadratic := by
  constructor
  · intro P hP f h
    exact translatedThresholdForm_polarized e he g hg hs CD hCD hquad hquarter heLower hquadratic P hP f h
  · intro P hP
    exact polarizedThreshold_terms_continuous e he g hg hs CD hCD hquad P hP

theorem finalOP03 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      ∃ hquarter : |g| ≤ 1/4,
      ∃ heLower : -sectorEnergyConstant*|g|^2 ≤ groundEnergy (fiberHamiltonian g 0),
      ∃ hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8,
      OP01FixedReference C CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad ∧
      OP03FixedReference (groundEnergy (fiberHamiltonian g 0)) he g hg hs CD hCD hquad hquarter heLower hquadratic := by
  obtain ⟨C,CD,s,hC,hCD,hs,h⟩ := finalOP02
  refine ⟨C,CD,s,hC,hCD,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hquarter,heLower,hquadratic,hOP,_⟩ := h g hgs
  exact ⟨he,hg,haux,hCD0,hquad,hquarter,heLower,hquadratic,hOP,
    finalOP03_reference _ he g hg haux CD hCD0 hquad hquarter heLower hquadratic⟩

end Froehlich
