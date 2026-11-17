import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.UV01InverseBounds
import Froehlich.Nodes.LD01

set_option autoImplicit false

/-! Cutoff h bounds use the weighted source dual and are uniform in the
cutoff and momentum. The unweighted cutoff coefficient norm is not used. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem pt03_cutoffSourceLoad_norm_le (g Lambda : ℝ) (P : GW.Space) :
    ‖cutoffFiberSourceLoad g P Lambda‖ ≤ ‖isolatedFiberSourceLoad g P‖ := by
  apply (fockWeightedSourceLoad_norm_le P (fun k => (cutoffFormFactor g Lambda k : ℂ))
    (cutoffFiberSource_quotient_memLp g Lambda P)).trans
  change ‖weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (cutoffFormFactor g Lambda k : ℂ)) _‖ ≤
    ‖weightedSourceLoad (oneParticleEnergyWeight P) (fun k => (fiberFormFactor g k : ℂ)) _‖
  rw [weightedSourceLoad_norm,weightedSourceLoad_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [weightedSourceCoordinate_ae (oneParticleEnergyWeight P)
      (fun k => (cutoffFormFactor g Lambda k : ℂ)) (cutoffFiberSource_quotient_memLp g Lambda P),
    weightedSourceCoordinate_ae (oneParticleEnergyWeight P)
      (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P)] with k hc hs
  rw [hc,hs]
  by_cases hk : ‖k‖ ≤ Lambda
  · simp only [cutoffFormFactor,if_pos hk,le_refl]
  · simp only [cutoffFormFactor,if_neg hk,Complex.ofReal_zero,zero_div,norm_zero]
    exact norm_nonneg _

theorem cutoffThresholdSourceVector_norm_le (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space) :
    ‖cutoffThresholdSourceVector e he g hg hs Lambda p‖ ≤ 6*‖isolatedFiberSourceLoad g (-p)‖ := by
  let F := cutoffHighFiberSourceLoad g (-p) 1 Lambda.val
  let A := cutoffAuxiliaryEnergyInverse 1 e p (by norm_num) he g hg hs Lambda
  have hF : ‖F‖ ≤ ‖cutoffFiberSourceLoad g (-p) Lambda.val‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (cutoffFiberSourceLoad g (-p) Lambda.val).le_opNorm (x : EnergySpace (-p))
  have hE : ‖cutoffThresholdSourceVector e he g hg hs Lambda p‖ ≤
      ‖cutoffGroundSourceEnergy e p he g hg hs Lambda‖ := by
    have hn : ‖(cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))‖ =
        ‖cutoffGroundSourceEnergy e p he g hg hs Lambda‖ := rfl
    have hm : ‖energyEmbedding (-p)‖ *
        ‖(cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))‖ ≤
        ‖(cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))‖ := by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right (energyEmbedding_opNorm (-p))
        (norm_nonneg (cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))))
    exact ((energyEmbedding (-p)).le_opNorm
      (cutoffGroundSourceEnergy e p he g hg hs Lambda : EnergySpace (-p))).trans (hm.trans_eq hn)
  have hsol : A (loadRiesz F) = cutoffGroundSourceEnergy e p he g hg hs Lambda :=
    cutoffAuxiliaryEnergyInverse_load 1 e p (by norm_num) he g hg hs Lambda F
  calc
    _ ≤ ‖cutoffGroundSourceEnergy e p he g hg hs Lambda‖ := hE
    _ = ‖A (loadRiesz F)‖ := congrArg norm hsol.symm
    _ ≤ ‖A‖*‖loadRiesz F‖ := A.le_opNorm _
    _ ≤ 6*‖F‖ := mul_le_mul (cutoffAuxiliaryEnergyInverse_norm_le 1 e p (by norm_num) he g hg hs Lambda)
      (le_of_eq (loadRiesz_norm F)) (norm_nonneg _) (by norm_num)
    _ ≤ 6*‖isolatedFiberSourceLoad g (-p)‖ := mul_le_mul_of_nonneg_left
      (hF.trans (pt03_cutoffSourceLoad_norm_le g Lambda.val (-p))) (by norm_num)

theorem cutoffThresholdSourceVector_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Lambda : GW.Operators.PositiveCutoff) (p : GW.Space),
      ‖cutoffThresholdSourceVector e he g hg hs Lambda p‖ ≤ C*|g| := by
  obtain ⟨Cv,hCv,hv⟩ := fiberSourceLoads_uniform_bound
  refine ⟨6*Real.sqrt Cv+1,by positivity,?_⟩
  intro g e he hg hs Lambda p
  have hL : ‖isolatedFiberSourceLoad g (-p)‖ ≤ Real.sqrt Cv*|g| := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg g))).mp
    rw [mul_pow,Real.sq_sqrt hCv.le,sq_abs]
    exact (hv g (-p)).1
  exact (cutoffThresholdSourceVector_norm_le e he g hg hs Lambda p).trans
    ((mul_le_mul_of_nonneg_left hL (by norm_num)).trans (by nlinarith [abs_nonneg g]))

end Froehlich
