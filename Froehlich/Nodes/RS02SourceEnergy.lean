import Froehlich.Nodes.RS02NormalizedSource

/-! The actual source solution has a weighted-domain representative, with
uniform zeroth-order bounds, at the same reference energy. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable (g e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

theorem auxiliaryNormalizedSource_pullback : auxiliaryNormalizedSource g e p he.2 =
    loadRiesz ((highFiberSourceLoad g (-p) 1).comp
      (auxiliaryEnergyLiftEquivalence 1 e p (by norm_num) he).toContinuousLinearMap) := by
  apply loadRiesz_unique
  intro u
  rw [auxiliaryNormalizedSource_pairing]
  change fiberSourceLoad g (-p)
    (auxiliaryEnergyLiftEquivalence 1 e p (by norm_num) he u : EnergySpace (-p)) = _
  rw [auxiliaryEnergyLiftEquivalence_val]

variable (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem auxiliaryGroundSourceEnergy_formula : auxiliaryGroundSourceEnergy e p he g hg hsmall =
    auxiliaryEnergyLiftEquivalence 1 e p (by norm_num) he
      (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)) := by
  change auxiliaryEnergyLiftEquivalence 1 e p (by norm_num) he
    (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (loadRiesz _)) = _
  rw [← auxiliaryNormalizedSource_pullback]

theorem auxiliaryGroundSourceVector_formula : auxiliaryGroundSourceVector e p he g hg hsmall =
    (auxiliaryPhysicalFreeInverse 1 e p he.2
      (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2)) : GW.Fock.Carrier) := by
  rw [auxiliaryGroundSourceVector,auxiliaryGroundSourceEnergy_formula]
  exact congrArg (fun u : HighSectorSpace 1 => (u : GW.Fock.Carrier))
    (auxiliaryEnergyLift_high_physical 1 e p (by norm_num) he _)

def auxiliaryGroundSourceWeighted : AuxiliaryEnergySpace 1 e p he.2 :=
  auxiliaryFreeInverseEnergy 1 e p he.2
    (auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall (auxiliaryNormalizedSource g e p he.2))

theorem auxiliaryGroundSourceWeighted_physical :
    (auxiliaryEnergyEmbedding 1 e p he.2 (auxiliaryGroundSourceWeighted g e p he hg hsmall) : GW.Fock.Carrier) =
      auxiliaryGroundSourceVector e p he g hg hsmall := by
  rw [auxiliaryGroundSourceVector_formula]
  rfl

theorem auxiliaryGroundSourceWeighted_norm_le :
    ‖auxiliaryGroundSourceWeighted g e p he hg hsmall‖ ≤ 2*‖auxiliaryNormalizedSource g e p he.2‖ := by
  rw [auxiliaryGroundSourceWeighted,LinearIsometryEquiv.norm_map]
  exact ((auxiliaryNormalizedInverse g 1 e p he.2 hg hsmall).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (auxiliaryNormalizedInverse_norm_le g 1 e p he.2 hg hsmall) (norm_nonneg _))

theorem auxiliaryGroundSourceWeighted_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (p : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2),
      ‖auxiliaryGroundSourceWeighted g e p he hg hsmall‖^2 ≤ C*g^2 := by
  obtain ⟨Cz,hCz,hz⟩ := auxiliaryNormalizedSources_uniform_bound
  refine ⟨4*Cz,by positivity,fun g e p he hg hsmall => ?_⟩
  have h := auxiliaryGroundSourceWeighted_norm_le g e p he hg hsmall
  have hsq := (sq_le_sq₀ (norm_nonneg (auxiliaryGroundSourceWeighted g e p he hg hsmall))
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (norm_nonneg _))).mpr h
  have hb := mul_le_mul_of_nonneg_left (hz g e p he.2) (by norm_num : (0:ℝ)≤4)
  nlinarith

end Froehlich
