import Froehlich.Nodes.SE03InfraredIdentity
import Froehlich.Nodes.SE03Nonintegrability
import Froehlich.Nodes.OP01Inverse

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hanchor : auxiliarySelfEnergy e 0 he g hg hs = e)
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)-1‖ ≤ 1/2)

include hquarter heLower hquadratic hanchor hN in
/-- Exact saturation of the actual zero-momentum inverse response, without c0 division. -/
theorem se03_saturation (hg0 : g ≠ 0) :
    ⟪thresholdKernelSourceVector e he g hg hs 0 (by simp),
      thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
        (thresholdKernelSourceVector e he g hg hs 0 (by simp))⟫_ℂ =
      (kernelConstant e he g hg hs 0 : ℂ) := by
  let b := thresholdKernelSourceVector e he g hg hs 0 (by simp)
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
  let R := thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
  let u := oneParticleRadialMap (groundSourceOneEnergy e he g hg hs)
  let d := se03InfraredDifference e he g hg hs CD hCD hquad
  let a := se03InfraredCoefficient e he g hg hs
  have hIR := se03_infrared_identity e he g hg hs CD hCD hquad
    hquarter heLower hquadratic hanchor
  have ha : a = 0 := se03_infrared_coefficient_eq_zero g hg0 d a hIR
  have hd : d = 0 := by
    apply Lp.ext
    filter_upwards [hIR,Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with q hq hz
    change d q = ((g/‖q‖^2 : ℝ) : ℂ)*a at hq
    rw [ha,mul_zero] at hq
    exact hq.trans hz.symm
  have hBu : B u = ((1+e : ℝ) : ℂ) • b := by
    have h : ((1+e : ℝ) : ℂ) • b-B u = 0 := hd
    exact (sub_eq_zero.mp h).symm
  have hpair : ⟪b,u⟫_ℂ = (((1+e)*kernelConstant e he g hg hs 0 : ℝ) : ℂ) := by
    have h : ⟪b,u⟫_ℂ-((1+e : ℝ) : ℂ)*(kernelConstant e he g hg hs 0 : ℂ) = 0 := ha
    simpa only [Complex.ofReal_mul] using sub_eq_zero.mp h
  have hR := (thresholdBoundedInverse_spec e he g hg hs CD hCD hquad 0 (by simp) hN).1
  have hRB : R.comp B = ContinuousLinearMap.id ℂ GW.OnePhonon := hR
  exact se03_saturation_of_cancelled_vectors B R b u (1+e) (kernelConstant e he g hg hs 0)
    (by linarith [he.1]) hRB hBu hpair

end Froehlich
