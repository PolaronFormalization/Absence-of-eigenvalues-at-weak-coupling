import Froehlich.Nodes.WE01NativeMultiplier
import Froehlich.Nodes.OP01GroundSmallness

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def thresholdInverseMultiplierCoefficient (q : GW.Space) : ℝ :=
  (thresholdDiagonalMultiplier e he g hg hs q)⁻¹

theorem thresholdInverseMultiplierCoefficient_measurable :
    Measurable (thresholdInverseMultiplierCoefficient e he g hg hs) :=
  (thresholdDiagonalMultiplier_measurable e he g hg hs).inv

variable (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)

include hLower in
theorem thresholdInverseMultiplierCoefficient_bound (q : GW.Space) :
    ‖thresholdInverseMultiplierCoefficient e he g hg hs q‖ ≤ (4/3 : ℝ) := by
  have hl := hLower q
  have hp : 0 < thresholdDiagonalMultiplier e he g hg hs q := by linarith
  rw [thresholdInverseMultiplierCoefficient,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),inv_eq_one_div]
  apply (div_le_iff₀ hp).mpr
  nlinarith

/-- Actual multiplication by the inverse of OP01's literal measurable m,
on the same ordinary real L-infinity space. -/
def thresholdInverseLinftyMultiplier :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  nativeLinftyMultiplier (thresholdInverseMultiplierCoefficient e he g hg hs)
    (thresholdInverseMultiplierCoefficient_measurable e he g hg hs) (4/3)
    (Eventually.of_forall (thresholdInverseMultiplierCoefficient_bound e he g hg hs hLower))

theorem thresholdInverseLinftyMultiplier_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    thresholdInverseLinftyMultiplier e he g hg hs hLower f =ᵐ[volume]
      (fun q => (thresholdDiagonalMultiplier e he g hg hs q)⁻¹*f q) :=
  nativeLinftyMultiplier_ae _ _ _ _ f

theorem thresholdInverseLinftyMultiplier_norm_le :
    ‖thresholdInverseLinftyMultiplier e he g hg hs hLower‖ ≤ (4/3 : ℝ) :=
  nativeLinftyMultiplier_norm_le _ _ _ (by norm_num) _

/-- The lower bound needed for the multiplier is constructed at the actual
ground energy, uniformly before signed coupling. -/
theorem thresholdInverseLinftyMultiplier_ground : ∃ s : ℝ, 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤
        thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      ‖thresholdInverseLinftyMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower‖ ≤ (4/3 : ℝ) := by
  obtain ⟨CD,C,s,hCD,hC,hs,hGround⟩ := op01_ground_smallness
  refine ⟨s,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hControl,hLower⟩ := hGround g hgs
  exact ⟨he,hg,haux,hLower,thresholdInverseLinftyMultiplier_norm_le _ he g hg haux hLower⟩

end Froehlich
