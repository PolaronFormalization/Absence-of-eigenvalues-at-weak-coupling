import Froehlich.Nodes.RS02ResolventBounds
import Froehlich.Nodes.RS02SourceDerivativesCompositionFinalBounds

set_option autoImplicit false
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ke01InputHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ke01InputEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01InputEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace

/-- The physical resolvent jet itself inherits the uniform bound of its
actual middle factor, since both surrounding G factors are contractions. -/
theorem ke01_auxiliaryResolvent_derivatives_uniform :
    ∀ alpha : Fin 3 → ℕ, (∑ i, alpha i) ≤ 3 → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
        (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
        (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial alpha
          (fun t => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C := by
  intro alpha ha
  obtain ⟨C,hC,hB⟩ := auxiliaryResolventMiddleJet_uniform alpha ha
  refine ⟨C,hC,?_⟩
  intro n e hn he g hg hs q
  rw [auxiliaryResolvent_multiPartial_factor alpha ha n e hn he g hg hs q]
  let p := (EuclideanSpace.equiv (Fin 3) ℝ).symm q
  let G := auxiliaryPhysicalFreeInverse n e p he.2
  let B := auxiliaryResolventMiddleJet alpha n e p he g hg hs
  have hG : ‖G‖ ≤ 1 := auxiliaryPhysicalFreeInverse_norm_le n e p he.2
  have hBn : ‖B‖ ≤ C := hB n e p hn he g hg hs
  have hi : ‖B.comp G‖ ≤ C :=
    (B.opNorm_comp_le G).trans (by nlinarith [norm_nonneg G,norm_nonneg B])
  exact (G.opNorm_comp_le (B.comp G)).trans
    (by nlinarith [norm_nonneg G,norm_nonneg (B.comp G)])

end Froehlich
