import Froehlich.Nodes.OP01GroundSmallness
import Froehlich.Nodes.OP01NearIdentity

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

def thresholdBoundedInverse : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
  nearIdentityInverse (thresholdBoundedOperator e he g hg hs C hC hquad P hP)

variable (hN : ‖thresholdBoundedOperator e he g hg hs C hC hquad P hP-1‖ ≤ 1/2)

include hN in
theorem thresholdBoundedInverse_spec :
    thresholdBoundedInverse e he g hg hs C hC hquad P hP * thresholdBoundedOperator e he g hg hs C hC hquad P hP = 1 ∧
    thresholdBoundedOperator e he g hg hs C hC hquad P hP * thresholdBoundedInverse e he g hg hs C hC hquad P hP = 1 ∧
    ‖thresholdBoundedInverse e he g hg hs C hC hquad P hP‖ ≤ 2 :=
  nearIdentityInverse_spec (thresholdBoundedOperator e he g hg hs C hC hquad P hP) hN

include hN in
theorem thresholdBoundedOperator_quadratic_lower (f : GW.OnePhonon) :
    ‖f‖^2/2 ≤ (⟪f,thresholdBoundedOperator e he g hg hs C hC hquad P hP f⟫_ℂ).re :=
  nearIdentity_quadratic_lower (thresholdBoundedOperator e he g hg hs C hC hquad P hP) hN f

include hN in
theorem thresholdBoundedInverse_selfadjoint :
    (thresholdBoundedInverse e he g hg hs C hC hquad P hP).adjoint =
      thresholdBoundedInverse e he g hg hs C hC hquad P hP := by
  have hI := thresholdBoundedInverse_spec e he g hg hs C hC hquad P hP hN
  exact inverse_selfadjoint _ _ (thresholdBoundedOperator_selfadjoint e he g hg hs C hC hquad P hP)
    hI.1 hI.2.1

include hN in
theorem thresholdBoundedInverse_conjugation (f : GW.OnePhonon) :
    thresholdBoundedInverse e he g hg hs C hC hquad P hP (conjugateOnePhonon f) =
      conjugateOnePhonon (thresholdBoundedInverse e he g hg hs C hC hquad P hP f) := by
  let B := thresholdBoundedOperator e he g hg hs C hC hquad P hP
  let I := thresholdBoundedInverse e he g hg hs C hC hquad P hP
  have hI := thresholdBoundedInverse_spec e he g hg hs C hC hquad P hP hN
  have hl : Function.LeftInverse I B := by
    intro u
    have h := congrArg (fun T : GW.OnePhonon →L[ℂ] GW.OnePhonon => T u) hI.1
    change I (B u) = u at h
    exact h
  have hr (u : GW.OnePhonon) : B (I u) = u := by
    have h := congrArg (fun T : GW.OnePhonon →L[ℂ] GW.OnePhonon => T u) hI.2.1
    exact h
  have hconj (u : GW.OnePhonon) : B (conjugateOnePhonon u) = conjugateOnePhonon (B u) :=
    thresholdBoundedOperator_conjugation e he g hg hs C hC hquad P hP u
  apply hl.injective
  change B (I (conjugateOnePhonon f)) = B (conjugateOnePhonon (I f))
  rw [hr,hconj,hr]

end Froehlich
