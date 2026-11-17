import Froehlich.Nodes.PT03FormSplit
import Froehlich.Nodes.PT03FormKernelLimit
import Froehlich.Nodes.PT03FormCorrectionLimit
import Froehlich.Nodes.PT03FormCorrectionSingular

set_option autoImplicit false

/-! Equality of the actual form-norm limit and the absolutely convergent
scalar limits. All cutoff operators use the same fixed reference e. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space)

theorem singularEnergySchurCorrection_kernel_formula (hP : ‖P‖ ≤ 1/4)
    (f h : OneParticleEnergySpace P) :
    ⟪f,singularEnergySchurCorrection e P he g hg hs h⟫_ℂ =
      (∫ k, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k) *
        (-(auxiliarySelfEnergy e (k-P) he g hg hs : ℂ)) * oneParticleEnergyEmbedding P h k) +
      ∫ x : GW.Space × GW.Space, thresholdJProduct e he g hg hs P f h x ∂volume.prod volume := by
  have hD := cutoffThresholdDiagonal_integral_tendsto e he g hg hs P
    (oneParticleEnergyEmbedding P f) (oneParticleEnergyEmbedding P h)
  have hJ := cutoffThresholdKernel_integral_tendsto e he g hg hs P hP f h
  have hEq (Λ : GW.Operators.PositiveCutoff) :
      ⟪f,cutoffEnergySchurCorrection e P he g hg hs Λ h⟫_ℂ =
        (∫ k, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k) *
          cutoffThresholdDiagonal e he g hg hs Λ (k-P) * oneParticleEnergyEmbedding P h k) +
        ∫ x : GW.Space × GW.Space, cutoffThresholdJProduct e he g hg hs P Λ f h x ∂volume.prod volume := by
    rw [cutoffEnergySchurCorrection_creation_pairing]
    exact (cutoffCorrection_split_integrals e he g hg hs P hP Λ f h).2.2
  have hScalar := (hD.add hJ).congr' (Eventually.of_forall (fun Λ => (hEq Λ).symm))
  exact tendsto_nhds_unique (cutoffEnergySchurCorrection_pairing_tendsto e P he g hg hs f h) hScalar

theorem thresholdCorrection_kernel_formula (hP : ‖P‖ ≤ 1/4)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (f h : OneParticleEnergySpace P) :
    ⟪f,onePhononHighCorrection g e 0 P hquarter heLower he.2 (by norm_num) hquadratic h⟫_ℂ =
      (∫ k, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k) *
        (-(auxiliarySelfEnergy e (k-P) he g hg hs : ℂ)) * oneParticleEnergyEmbedding P h k) +
      ∫ x : GW.Space × GW.Space, thresholdJProduct e he g hg hs P f h x ∂volume.prod volume := by
  rw [←singularEnergySchurCorrection_eq_threshold e P he g hg hs hquarter heLower hquadratic]
  exact singularEnergySchurCorrection_kernel_formula e he g hg hs P hP f h

end Froehlich
