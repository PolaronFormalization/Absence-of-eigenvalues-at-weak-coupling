import Froehlich.Nodes.KE01JDerivativeBounds
import Froehlich.Nodes.KE01DenominatorNineBounds
import Froehlich.Nodes.KE01CanonicalNormLocal

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem thresholdKernelC_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3)
      (x : Fin 9 → ℝ), ‖kernelCoordinateBlock 0 x‖ ≤ 1/4 →
      ‖iteratedFDeriv ℝ k (thresholdKernelCCoordinates e he g hg hs) x‖ ≤ C := by
  obtain ⟨CD,hCD,hD⟩ := kernelDenominatorNine_iterated_uniform
  obtain ⟨CJ,hCJ,hJ⟩ := thresholdKernelJ_iterated_uniform
  refine ⟨CD+CJ,by positivity,?_⟩
  intro e he g hg hs k hk x hx
  let D := fun y : Fin 9 → ℝ => (((1+e-‖kernelCoordinateBlock 0 y‖^2)⁻¹ : ℝ) : ℂ)
  have hsmall : ‖kernelCoordinateBlock 0 x‖ < 1/3 := by linarith
  have hD3 : ContDiffAt ℝ 3 D x := by
    have h := (ke01_denominator_contDiffAt e he (kernelJointCoordinates x) hsmall).comp x
      kernelJointCoordinates.contDiff.contDiffAt
    simpa only [D,Function.comp_def,kernelJointCoordinates_apply] using! h
  have hJ3 : ContDiff ℝ 3 (thresholdKernelJCoordinates e he g hg hs) :=
    thresholdKernelJCoordinates_contDiff e he g hg hs
  have hfun : thresholdKernelCCoordinates e he g hg hs = D-thresholdKernelJCoordinates e he g hg hs := by
    funext y
    rfl
  have hsub := iteratedFDeriv_sub_apply (x := x)
    (hD3.of_le (by exact_mod_cast hk)) (hJ3.of_le (by exact_mod_cast hk)).contDiffAt
  rw [hfun,hsub]
  exact (norm_sub_le _ _).trans (add_le_add (hD e he k hk x hx) (hJ e he g hg hs k hk x))

/-- All canonical ordinary mixed partials through order three share the same
constant. Closed-ball boundary points use the genuine open-third derivative. -/
theorem thresholdKernelC_multiPartial_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (alpha : Fin 9 → ℕ)
      (ha : (∑ i,alpha i) ≤ 3) (x : Fin 9 → ℝ), ‖kernelCoordinateBlock 0 x‖ ≤ 1/4 →
      ‖coordinateMultiPartial alpha (thresholdKernelCCoordinates e he g hg hs) x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := thresholdKernelC_iterated_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs alpha ha x hx
  have hAt : ContDiffAt ℝ (∑ i,alpha i : ℕ) (thresholdKernelCCoordinates e he g hg hs) x :=
    (thresholdKernelCCoordinates_contDiffAt_closedBall e he g hg hs x hx).of_le (by exact_mod_cast ha)
  exact (coordinateMultiPartial_norm_le_iterated_at alpha
    (thresholdKernelCCoordinates e he g hg hs) x hAt).trans
      (hB e he g hg hs (∑ i,alpha i) ha x hx)

end Froehlich
