import Froehlich.Nodes.KE01PhysicalDerivativeBounds
import Froehlich.Nodes.KE01KernelSymmetry
import Froehlich.Nodes.KE01KernelReflection
import Froehlich.Nodes.RS01Anchors

set_option autoImplicit false

/-! KE01 / lem:Cregularity. Literal complex kernel, proved reality and
symmetries, ordinary open-neighborhood derivatives, and a single uniform
constant for all nine-coordinate derivatives through total order three. -/
noncomputable section
namespace Froehlich

def KE01SymmetryReference (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ P q r : GW.Space, ((thresholdKernelC e he g hg hs P q r).re : ℂ) = thresholdKernelC e he g hg hs P q r) ∧
  (∀ P q r : GW.Space, thresholdKernelC e he g hg hs P q r = thresholdKernelC e he g hg hs P r q) ∧
  ∀ P q r : GW.Space, thresholdKernelC e he g hg hs (-P) (-q) (-r) = thresholdKernelC e he g hg hs P q r

def KE01DerivativeReference (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  (∀ t : GW.Space × (GW.Space × GW.Space), ‖t.1‖ < 1/3 →
    ContDiffAt ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2) t) ∧
  (∀ x : Fin 9 → ℝ, ‖kernelCoordinateBlock 0 x‖ ≤ 1/4 →
    ContDiffAt ℝ 3 (thresholdKernelCCoordinates e he g hg hs) x) ∧
  (∀ (alpha : Fin 9 → ℕ), (∑ i,alpha i) ≤ 3 → ∀ P q r : GW.Space, ‖P‖ ≤ 1/4 →
    ‖coordinateMultiPartial alpha (thresholdKernelCCoordinates e he g hg hs) (kernelCoordinatesFor P q r)‖ ≤ C) ∧
  ∀ k : ℕ, k ≤ 3 → ∀ t : GW.Space × (GW.Space × GW.Space), ‖t.1‖ ≤ 1/4 →
    ‖iteratedFDeriv ℝ k (fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2) t‖ ≤ C

def KE01FixedReference (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) : Prop :=
  KE01SymmetryReference e he g hg hs ∧ KE01DerivativeReference C e he g hg hs ∧
  ∀ P q r : GW.Space, thresholdKernelC e he g hg hs P q r =
    ((kernelConstant e he g hg hs P+kernelPsi e he g hg hs P q+
      kernelPsi e he g hg hs P r+remainderKernel e he g hg hs P q r : ℝ) : ℂ)

theorem finalKE01_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2), KE01FixedReference C e he g hg hs := by
  obtain ⟨A,hA,hAB⟩ := thresholdKernelC_physical_multiPartial_uniform
  obtain ⟨B,hB,hBB⟩ := thresholdKernelC_product_iterated_uniform
  refine ⟨A+B,by positivity,?_⟩
  intro e he g hg hs
  refine ⟨⟨thresholdKernelC_ofReal_re e he g hg hs,thresholdKernelC_symmetric e he g hg hs,
    thresholdKernelC_reflection e he g hg hs⟩,?_,thresholdKernelC_decomposition e he g hg hs⟩
  refine ⟨thresholdKernelC_contDiffAt e he g hg hs,
    thresholdKernelCCoordinates_contDiffAt_closedBall e he g hg hs,?_,?_⟩
  · intro alpha ha P q r hP
    exact (hAB e he g hg hs alpha ha P q r hP).trans (le_add_of_nonneg_right hB.le)
  · intro k hk t ht
    exact (hBB e he g hg hs k hk t ht).trans (le_add_of_nonneg_left hA.le)

theorem finalKE01 : ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ g : ℝ, |g| < s →
    ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
    ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      KE01FixedReference C (groundEnergy (fiberHamiltonian g 0)) he g hg hs := by
  obtain ⟨C,hC,hB⟩ := finalKE01_uniform
  obtain ⟨s,hs,hGround⟩ := auxiliarySelfEnergy_zero_groundEnergy
  refine ⟨C,s,hC,hs,?_⟩
  intro g hgSmall
  obtain ⟨he,hg,hsmall,_⟩ := hGround g hgSmall
  exact ⟨he,hg,hsmall,hB _ he g hg hsmall⟩

end Froehlich
