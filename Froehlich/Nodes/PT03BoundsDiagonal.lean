import Froehlich.Nodes.PT03BoundsCutoffSource
import Froehlich.Nodes.PT02SourceConvergence
import Froehlich.Nodes.RS03StaticBounded

set_option autoImplicit false

/-! The actual cutoff diagonal is a weighted source-dual pairing. Its
uniform O(g²) bound and limit never use unweighted convergence of vLambda. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffThresholdDiagonal (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space) : ℂ :=
  (starRingEnd ℂ) (cutoffHighFiberSourceLoad g (-p) 1 Lambda.val
    (cutoffGroundSourceEnergy e p he g hg hs Lambda))

theorem cutoffThresholdDiagonal_hilbert (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space) :
    cutoffThresholdDiagonal e he g hg hs Lambda p =
      ⟪oneParticleInclusion (cutoffFormFactorL2 g Lambda.val Lambda.property),
        cutoffAuxiliaryY e p he Lambda g hg hs
          (oneParticleInclusion (cutoffFormFactorL2 g Lambda.val Lambda.property))⟫_ℂ := by
  change (starRingEnd ℂ) (cutoffHighFiberSourceLoad g (-p) 1 Lambda.val
    (cutoffGroundSourceEnergy e p he g hg hs Lambda)) =
    ⟪(cutoffOneParticleSource g Lambda : GW.Fock.Carrier),
      cutoffAuxiliaryExtendedResolvent 1 e p he Lambda g hg hs (cutoffOneParticleSource g Lambda : GW.Fock.Carrier)⟫_ℂ
  rw [cutoffOneParticleSource_load,cutoffAuxiliaryExtendedResolvent_on_high,
    ←cutoffGroundSourceEnergy_physical]
  exact inner_conj_symm _ _

private theorem pt03_cutoffHighLoad_norm (g : ℝ) (p : GW.Space) (Lambda : GW.Operators.PositiveCutoff) :
    ‖cutoffHighFiberSourceLoad g (-p) 1 Lambda.val‖ ≤ ‖isolatedFiberSourceLoad g (-p)‖ := by
  have h : ‖cutoffHighFiberSourceLoad g (-p) 1 Lambda.val‖ ≤ ‖cutoffFiberSourceLoad g (-p) Lambda.val‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (cutoffFiberSourceLoad g (-p) Lambda.val).le_opNorm (x : EnergySpace (-p))
  exact h.trans (pt03_cutoffSourceLoad_norm_le g Lambda.val (-p))

include he hg hs in
theorem cutoffThresholdDiagonal_norm_le (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space) :
    ‖cutoffThresholdDiagonal e he g hg hs Lambda p‖ ≤ 6*‖isolatedFiberSourceLoad g (-p)‖^2 := by
  let F := cutoffHighFiberSourceLoad g (-p) 1 Lambda.val
  let A := cutoffAuxiliaryEnergyInverse 1 e p (by norm_num) he g hg hs Lambda
  have hsol : A (loadRiesz F) = cutoffGroundSourceEnergy e p he g hg hs Lambda :=
    cutoffAuxiliaryEnergyInverse_load 1 e p (by norm_num) he g hg hs Lambda F
  have hnorm : ‖cutoffGroundSourceEnergy e p he g hg hs Lambda‖ ≤ 6*‖F‖ := by
    rw [←hsol]
    exact (A.le_opNorm _).trans (by
      rw [loadRiesz_norm]
      exact mul_le_mul_of_nonneg_right (cutoffAuxiliaryEnergyInverse_norm_le 1 e p (by norm_num) he g hg hs Lambda)
        (norm_nonneg F))
  have hF := pt03_cutoffHighLoad_norm g p Lambda
  have h1 : ‖F (cutoffGroundSourceEnergy e p he g hg hs Lambda)‖ ≤ ‖F‖*(6*‖F‖) :=
    (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg F))
  have h2 := mul_le_mul hF (mul_le_mul_of_nonneg_left hF (by norm_num : (0:ℝ)≤6))
    (mul_nonneg (by norm_num) (norm_nonneg F)) (norm_nonneg (isolatedFiberSourceLoad g (-p)))
  change ‖(starRingEnd ℂ) (F _)‖ ≤ _
  rw [RCLike.norm_conj]
  exact h1.trans (h2.trans_eq (by ring))

theorem cutoffThresholdDiagonal_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space),
      ‖cutoffThresholdDiagonal e he g hg hs Lambda p‖ ≤ C*g^2 := by
  obtain ⟨Cv,hCv,hv⟩ := fiberSourceLoads_uniform_bound
  refine ⟨6*Cv,by positivity,?_⟩
  intro g e he hg hs Lambda p
  exact (cutoffThresholdDiagonal_norm_le e he g hg hs Lambda p).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hv g (-p)).1 (by norm_num : (0:ℝ)≤6))

theorem cutoffThresholdDiagonal_tendsto (p : GW.Space) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffThresholdDiagonal e he g hg hs Lambda p)
      atTop (𝓝 (-(auxiliarySelfEnergy e p he g hg hs : ℂ))) := by
  let F := highFiberSourceLoad g (-p) 1
  let x := auxiliaryGroundSourceEnergy e p he g hg hs
  have hTotal := (cutoffFiberSourceLoad_tendsto g (-p)).comp positiveCutoff_coe_tendsto
  have hLoad : Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffHighFiberSourceLoad g (-p) 1 Lambda.val)
      atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun Lambda => norm_nonneg _) _ (tendsto_iff_norm_sub_tendsto_zero.mp hTotal)
    intro Lambda
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro u
    exact (cutoffFiberSourceLoad g (-p) Lambda.val-fiberSourceLoad g (-p)).le_opNorm (u : EnergySpace (-p))
  have hRiesz : Tendsto (fun Lambda : GW.Operators.PositiveCutoff =>
      loadRiesz (cutoffHighFiberSourceLoad g (-p) 1 Lambda.val)) atTop (𝓝 (loadRiesz F)) :=
    ((loadRieszLinearIsometry (V := HighEnergySpace (-p) 1)).continuous.tendsto F).comp hLoad
  have hPair := (cutoffGroundSourceEnergy_tendsto e p he g hg hs).inner (𝕜 := ℂ) hRiesz
  have hVal : F x = -(auxiliarySelfEnergy e p he g hg hs : ℂ) := by
    rw [auxiliaryGroundSourceEnergy_bounded_pairing,auxiliarySelfEnergy_bounded_complex,neg_neg]
  have hDual : Tendsto (fun Lambda : GW.Operators.PositiveCutoff =>
      cutoffHighFiberSourceLoad g (-p) 1 Lambda.val (cutoffGroundSourceEnergy e p he g hg hs Lambda))
      atTop (𝓝 (F x)) := by
    simpa only [loadRiesz_spec] using hPair
  have hstar := (Complex.conjCLE.continuous.tendsto (F x)).comp hDual
  simpa only [Function.comp_def,cutoffThresholdDiagonal,hVal,map_neg,Complex.conjCLE_apply,Complex.conj_ofReal] using hstar

end Froehlich
