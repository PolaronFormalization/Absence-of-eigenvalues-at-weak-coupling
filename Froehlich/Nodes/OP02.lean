import Froehlich.Nodes.OP02DiagonalIdentity
import Froehlich.Nodes.OP01
import Froehlich.Nodes.PT03FormCorrectionGround

set_option autoImplicit false

/-! OP02 / lem:unnormalizedform. Literal actual translated threshold form,
complete Q1 inputs and native radial map. At zero momentum the source is
retained as a continuous functional; the Hilbert source is only nonzero-P. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

def OP02FixedReference (CD e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) : Prop :=
  ‖oneParticleRadialMap‖ ≤ 1 ∧
  (∀ f : OneParticleEnergySpace 0, oneParticleRadialMap f =ᵐ[volume]
    (fun q => (‖q‖ : ℂ)*oneParticleEnergyEmbedding 0 f q)) ∧
  (∀ (P : GW.Space) (f : OneParticleEnergySpace 0),
    Integrable (fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)*oneParticleEnergyEmbedding 0 f q) volume ∧
    translatedLinearSource g P f = ∫ q : GW.Space,(fiberFormFactor g (q+P) : ℂ)*oneParticleEnergyEmbedding 0 f q) ∧
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f : OneParticleEnergySpace 0),
    translatedThresholdForm e he g hquarter heLower hquadratic P hP f f =
      ⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap f)⟫_ℂ+
      ((kernelConstant e he g hg hs P*‖translatedLinearSource g P f‖^2 : ℝ) : ℂ)+
      ((2*((starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap f⟫_ℂ).re : ℝ) : ℂ)) ∧
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4) (f : OneParticleEnergySpace 0),
    (translatedThresholdForm e he g hquarter heLower hquadratic P hP f f).re =
      (⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap f)⟫_ℂ).re+
      kernelConstant e he g hg hs P*‖translatedLinearSource g P f‖^2+
      2*((starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap f⟫_ℂ).re) ∧
  ∀ (P : GW.Space) (hP : P ≠ 0) (f : OneParticleEnergySpace 0),
    translatedLinearSource g P f = ⟪translatedHilbertSource g P hP,oneParticleRadialMap f⟫_ℂ

theorem finalOP02_reference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) :
    OP02FixedReference CD e he g hg hs hCD hquad hquarter heLower hquadratic := by
  refine ⟨oneParticleRadialMap_norm_le,oneParticleRadialMap_ae,?_,?_,?_,?_⟩
  · intro P f
    exact ⟨translatedLinearSource_integrable g P f,translatedLinearSource_integral g P f⟩
  · intro P hP f
    exact translatedThresholdForm_unnormalized e he g hg hs CD hCD hquad hquarter heLower hquadratic P hP f
  · intro P hP f
    exact translatedThresholdForm_unnormalized_real e he g hg hs CD hCD hquad hquarter heLower hquadratic P hP f
  · exact translatedLinearSource_eq_hilbert_radial g

theorem finalOP02 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
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
      OP02FixedReference CD (groundEnergy (fiberHamiltonian g 0)) he g hg hs hCD hquad hquarter heLower hquadratic := by
  obtain ⟨C,CD,sO,hC,hCD,hsO,hO⟩ := finalOP01
  obtain ⟨sT,hsT,hT⟩ := pt03_ground_reference_smallness
  let s := min sO sT
  refine ⟨C,CD,s,hC,hCD,lt_min hsO hsT,?_⟩
  intro g hgs
  have hgO : |g| < sO := hgs.trans_le (min_le_left _ _)
  have hgT : |g| < sT := hgs.trans_le (min_le_right _ _)
  obtain ⟨he,hg,haux,hCD0,hquad,hOP⟩ := hO g hgO
  obtain ⟨_he,_hg,_haux,hquarter,heLower,hquadratic⟩ := hT g hgT
  exact ⟨he,hg,haux,hCD0,hquad,hquarter,heLower,hquadratic,hOP,
    finalOP02_reference _ he g hg haux CD hCD0 hquad hquarter heLower hquadratic⟩

end Froehlich
