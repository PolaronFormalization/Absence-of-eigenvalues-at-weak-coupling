import Froehlich.Nodes.WE05
import Froehlich.Nodes.OP02RadialCancellation

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- N is defined at every momentum, including zero. -/
def thresholdScalarN : ℝ :=
  (⟪thresholdKernelSourceVector e he g hg hs P hP,
    thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
      (thresholdKernelSourceVector e he g hg hs P hP)⟫_ℂ).re

/-- The Hilbert source t is used only at a nonzero momentum. -/
def thresholdScalarU (hP0 : P ≠ 0) : ℂ :=
  ⟪thresholdKernelSourceVector e he g hg hs P hP,
    thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
      (translatedHilbertSource g P hP0)⟫_ℂ

def thresholdScalarT (hP0 : P ≠ 0) : ℝ :=
  (⟪translatedHilbertSource g P hP0,
    thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
      (translatedHilbertSource g P hP0)⟫_ℂ).re

/-- A self-adjoint inverse has genuinely real diagonal pairings. -/
theorem we06_selfadjoint_pairing_ofReal (R : GW.OnePhonon →L[ℂ] GW.OnePhonon)
    (hR : R.adjoint = R) (v : GW.OnePhonon) :
    ((⟪v,R v⟫_ℂ).re : ℂ) = ⟪v,R v⟫_ℂ := by
  have hs : ⟪R v,v⟫_ℂ = ⟪v,R v⟫_ℂ := by
    simpa only [hR] using R.adjoint_inner_left v v
  have hi := congrArg Complex.im hs
  have hc := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) v (R v))
  simp only [Complex.conj_im] at hc
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    linarith

variable (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ 1/2)

include hN in
theorem thresholdScalarN_ofReal :
    (thresholdScalarN e he g hg hs CD hCD hquad P hP : ℂ) =
      ⟪thresholdKernelSourceVector e he g hg hs P hP,
        thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
          (thresholdKernelSourceVector e he g hg hs P hP)⟫_ℂ :=
  we06_selfadjoint_pairing_ofReal _
    (thresholdBoundedInverse_selfadjoint e he g hg hs CD hCD hquad P hP hN) _

include hN in
theorem thresholdScalarT_ofReal (hP0 : P ≠ 0) :
    (thresholdScalarT e he g hg hs CD hCD hquad P hP hP0 : ℂ) =
      ⟪translatedHilbertSource g P hP0,
        thresholdBoundedInverse e he g hg hs CD hCD hquad P hP
          (translatedHilbertSource g P hP0)⟫_ℂ :=
  we06_selfadjoint_pairing_ofReal _
    (thresholdBoundedInverse_selfadjoint e he g hg hs CD hCD hquad P hP hN) _

end Froehlich
