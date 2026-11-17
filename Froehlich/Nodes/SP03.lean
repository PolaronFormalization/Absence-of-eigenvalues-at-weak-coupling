import Froehlich.Nodes.SP03Resolvent

/-! SP03: source near-resolvent lemma on the actual full form and maximal Hamiltonian domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem onePhononVacuumDenominator_zero_bound (e eps : ℝ) (P : GW.Space)
    (heps : 0 ≤ eps) (hd : 1/2 ≤ onePhononVacuumDenominator e eps P) :
    1/2 ≤ onePhononVacuumDenominator e 0 P := by
  unfold onePhononVacuumDenominator at *
  linarith

variable (g e eps : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (heLower : -sectorEnergyConstant*|g|^2 ≤ e) (he : e ≤ 0)
    (heps : 0 ≤ eps) (hsmall : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hd : 1/2 ≤ onePhononVacuumDenominator e eps P)
    (hc : onePhononCorrectionConstant*|g|^2 ≤ 1/2)

include hc in
theorem finalSP03 :
    ‖twoSectorEnergyInverse g e eps P hg heLower he heps hsmall‖ ≤ 8 ∧ ‖twoSectorPhysicalInverse g e eps P hg heLower he heps hsmall‖ ≤ 4 ∧
    (∀ f : OneParticleEnergySpace P,
      0 ≤ (⟪f,(onePhononHighCorrection g e eps P hg heLower he heps hsmall) f⟫_ℂ).re ∧
      (⟪f,(onePhononHighCorrection g e eps P hg heLower he heps hsmall) f⟫_ℂ).re ≤ onePhononCorrectionConstant*|g|^2*‖f‖^2 ∧
      1/2*onePhononKineticNorm P f^2-1/2*‖oneParticleEnergyEmbedding P f‖^2 ≤
        (⟪f,(onePhononSchurOperator g e eps P hg heLower he heps hsmall hd) f⟫_ℂ).re ∧
      eps*‖oneParticleEnergyEmbedding P f‖^2+(⟪f,(onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall (onePhononVacuumDenominator_zero_bound e eps P heps hd)) f⟫_ℂ).re ≤
        (⟪f,(onePhononSchurOperator g e eps P hg heLower he heps hsmall hd) f⟫_ℂ).re) ∧
    ((∀ f : OneParticleEnergySpace P, 0 ≤ (⟪f,(onePhononSchurOperator g e 0 P hg heLower he (by norm_num) hsmall (onePhononVacuumDenominator_zero_bound e eps P heps hd)) f⟫_ℂ).re) →
      0 < eps → e+1-eps ∈ realResolventSet (fiberHamiltonian g P)) := by
  refine ⟨twoSectorEnergyInverse_norm_le g e eps P hg heLower he heps hsmall,
    twoSectorPhysicalInverse_norm_le g e eps P hg heLower he heps hsmall,?_,?_⟩
  · intro f
    exact ⟨onePhononHighCorrection_nonnegative g e eps P hg heLower he heps hsmall f,
      onePhononHighCorrection_bound g e eps P hg heLower he heps hsmall f,
      onePhononSchurOperator_graph_lower g e eps P hg heLower he heps hsmall hd hc f,
      onePhononSchurOperator_monotone g e eps P hg heLower he heps hsmall hd (onePhononVacuumDenominator_zero_bound e eps P heps hd) f⟩
  · intro hzero hpos
    exact onePhonon_nonnegative_mem_resolvent g e eps P hg heLower he hpos hsmall hd
      (onePhononVacuumDenominator_zero_bound e eps P heps hd) hc hzero

end Froehlich
