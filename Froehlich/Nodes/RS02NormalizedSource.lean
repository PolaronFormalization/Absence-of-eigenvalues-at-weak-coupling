import Froehlich.Nodes.RS01

/-! RS02's normalized singular source is a genuine physical vector, defined
by the actual continuous conjugate load composed with the weighted inverse.
The uncut form factor itself is never treated as a Hilbert vector. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def auxiliaryNormalizedSource (g e : ℝ) (p : GW.Space) (he : e ≤ 0) : HighSectorSpace 1 :=
  loadRiesz ((fiberSourceLoad g (-p)).comp (auxiliaryEnergyLift 1 e p he))

theorem auxiliaryNormalizedSource_pairing (g e : ℝ) (p : GW.Space) (he : e ≤ 0)
    (u : HighSectorSpace 1) :
    ⟪u,auxiliaryNormalizedSource g e p he⟫_ℂ =
      fiberSourceLoad g (-p) (auxiliaryEnergyLift 1 e p he u) :=
  (loadRiesz_spec ((fiberSourceLoad g (-p)).comp (auxiliaryEnergyLift 1 e p he)) u).symm

theorem auxiliaryNormalizedSource_norm_le (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliaryNormalizedSource g e p he‖ ≤ Real.sqrt 3 * ‖fiberSourceLoad g (-p)‖ := by
  have hL : ‖auxiliaryEnergyLift 1 e p he‖ ≤ Real.sqrt 3 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    exact auxiliaryEnergyLift_norm_le 1 e p he
  rw [auxiliaryNormalizedSource,loadRiesz_norm]
  exact ((fiberSourceLoad g (-p)).opNorm_comp_le (auxiliaryEnergyLift 1 e p he)).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hL (norm_nonneg (fiberSourceLoad g (-p))))

theorem auxiliaryNormalizedSources_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (p : GW.Space) (he : e ≤ 0),
      ‖auxiliaryNormalizedSource g e p he‖^2 ≤ C*g^2 := by
  obtain ⟨Cv,hCv,hv⟩ := fiberSourceLoads_uniform_bound
  refine ⟨3*Cv,by positivity,fun g e p he => ?_⟩
  have hn := auxiliaryNormalizedSource_norm_le g e p he
  have hs := (sq_le_sq₀ (norm_nonneg (auxiliaryNormalizedSource g e p he))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hn
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)] at hs
  exact hs.trans (by
    have h := mul_le_mul_of_nonneg_left (hv g (-p)).2 (by norm_num : (0:ℝ)≤3)
    simpa only [mul_assoc] using h)

end Froehlich
