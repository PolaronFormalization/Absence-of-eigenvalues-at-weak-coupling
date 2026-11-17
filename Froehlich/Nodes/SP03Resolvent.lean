import Froehlich.Nodes.SP03FullEnergyRight
import Froehlich.Nodes.SP03OperatorSymmetry

/-! The full physical maximal-domain resolvent from the source Schur elimination. -/
noncomputable section
namespace Froehlich
variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 < eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hd0 : 1/2 ≤ onePhononVacuumDenominator e 0 P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)
    (hzero : ∀ f : OneParticleEnergySpace P,
      0 ≤ (inner ℂ f (onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall hd0 f)).re)

theorem onePhononFullEnergyInverse_right :
    (vacuumEnergyOperator g P (e+1-eps)) * (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero) = 1 := by
  apply ContinuousLinearMap.ext
  intro q
  exact onePhononFullEnergyInverse_right_apply g e eps P hg heLower he heps hsmall hd hd0 hc hzero q

theorem onePhononFullEnergyInverse_left :
    (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero) * (vacuumEnergyOperator g P (e+1-eps)) = 1 :=
  vacuumEnergyOperator_left_of_right g P (e+1-eps) (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero)
    (onePhononFullEnergyInverse_right g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

include hg heLower he heps hsmall hd hd0 hc hzero in
theorem onePhonon_nonnegative_mem_resolvent :
    e+1-eps ∈ realResolventSet (fiberHamiltonian g P) := by
  refine ⟨physicalEnergyInverse (fiberFormData g P none) (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero),?_⟩
  exact physicalEnergyInverse_isResolvent (fiberFormData g P none) (e+1-eps)
    (vacuumEnergyOperator g P (e+1-eps)) (onePhononFullEnergyInverse g e eps P hg heLower he heps hsmall hd hd0 hc hzero)
    (vacuumEnergyOperator_spec g P (e+1-eps))
    (onePhononFullEnergyInverse_left g e eps P hg heLower he heps hsmall hd hd0 hc hzero)
    (onePhononFullEnergyInverse_right g e eps P hg heLower he heps hsmall hd hd0 hc hzero)

end Froehlich
