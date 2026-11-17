import Froehlich.Nodes.SE01SourceProjection
import Froehlich.Nodes.KE01KernelDefinitions
import Froehlich.Nodes.PT03KernelMeasurability
import Froehlich.Nodes.PT03BoundsKernels

/-! PT02 at zero and the literal real Seiringer lambda. The real c/psi
objects are the shared KE01 definitions, not competing definitions. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def groundSourceZeroNumber : NumberFormSpace :=
  energyNumberCoordinates 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)

theorem groundSourceZeroNumber_eq : groundSourceZeroNumber e he g hg hs = groundSourceNumber e 0 he g hg hs := by
  apply numberFormEmbedding_injective
  rw [groundSourceZeroNumber,energyNumberCoordinates_intertwines,
    groundSourceZeroEnergy_physical,groundSourceNumber_physical]

theorem groundSource_zero_pullthrough_local (K : Set GW.Space) (hK : MeasurableSet K)
    (hKb : Bornology.IsBounded K) (R : ℝ) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (groundSourceZeroNumber e he g hg hs)) =
    (HighSectorSpace 0).subtypeL.compLp
      (localSingularInverseField 0 e 0 (by norm_num) he g hg hs K hK hKb
        (sourcePullthroughLocalField K (auxiliaryGroundSourceVector e 0 he g hg hs)
          (fun k => (fiberFormFactor g k : ℂ))
          (regularSource_local_formFactor_memLp g K hK R hKR))) := by
  rw [groundSourceZeroNumber_eq]
  exact groundSource_pullthrough_local e 0 he g hg hs K hK hKb R hKR

theorem groundSource_zero_pullthrough :
    ∀ᵐ k ∂volume, annihilationField (groundSourceZeroNumber e he g hg hs) k =
      (fiberFormFactor g k : ℂ) • auxiliaryZ e k he g hg hs
        (GW.Fock.vacuum-auxiliaryGroundSourceVector e 0 he g hg hs) := by
  rw [groundSourceZeroNumber_eq]
  simpa only [zero_add] using groundSource_pullthrough_global e 0 he g hg hs

def groundSourceLambda (k : GW.Space) : ℝ := (thresholdKernelJ e he g hg hs 0 k 0).re

theorem groundSourceLambda_ofReal (k : GW.Space) :
    (groundSourceLambda e he g hg hs k : ℂ) = thresholdKernelJ e he g hg hs 0 k 0 :=
  thresholdKernelJ_ofReal_re e he g hg hs 0 k 0

theorem groundSourceLambda_physical (k : GW.Space) :
    (groundSourceLambda e he g hg hs k : ℂ) =
      ⟪GW.Fock.vacuum-auxiliaryGroundSourceVector e k he g hg hs,
        auxiliaryZ e k he g hg hs (GW.Fock.vacuum-auxiliaryGroundSourceVector e 0 he g hg hs)⟫_ℂ +
      ⟪auxiliaryGroundSourceVector e k he g hg hs,
        auxiliaryX e he g hg hs 0 (auxiliaryGroundSourceVector e 0 he g hg hs)⟫_ℂ := by
  rw [groundSourceLambda_ofReal]
  simp only [thresholdKernelJ,zero_add,add_zero]

theorem groundSourceLambda_continuous : Continuous (groundSourceLambda e he g hg hs) := by
  have hm : Continuous (fun k : GW.Space => ((0 : GW.Space),(k,(0 : GW.Space)))) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  have hJ : Continuous (fun t : GW.Space × (GW.Space × GW.Space) =>
      thresholdKernelJ e he g hg hs t.1 t.2.1 t.2.2) :=
    thresholdKernelJ_continuous e he g hg hs
  have hcomposed := hJ.comp hm
  have hsection : Continuous (fun k : GW.Space => thresholdKernelJ e he g hg hs 0 k 0) := by
    simpa only [Function.comp_def] using! hcomposed
  change Continuous (fun k : GW.Space => (thresholdKernelJ e he g hg hs 0 k 0).re)
  exact Complex.continuous_re.comp hsection

theorem kernelConstant_zero_lambda : kernelConstant e he g hg hs 0 =
    (1+e)⁻¹-groundSourceLambda e he g hg hs 0 := by
  simp only [kernelConstant,thresholdKernelC,groundSourceLambda,Complex.sub_re,Complex.ofReal_re,
    norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero]

theorem kernelPsi_zero_lambda (k : GW.Space) : kernelPsi e he g hg hs 0 k =
    groundSourceLambda e he g hg hs 0-groundSourceLambda e he g hg hs k := by
  unfold kernelPsi
  rw [kernelConstant_zero_lambda]
  simp only [thresholdKernelC,groundSourceLambda,Complex.sub_re,Complex.ofReal_re,
    norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero]
  ring

theorem groundSourceLambda_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant * |g| ≤ 1/2) (k : GW.Space),
      |groundSourceLambda e he g hg hs k| ≤ C := by
  obtain ⟨C,hC,hBound⟩ := thresholdKernels_uniform_bound
  refine ⟨C,hC,?_⟩
  intro e he g hg hs k
  exact (Complex.abs_re_le_norm (thresholdKernelJ e he g hg hs 0 k 0)).trans
    ((hBound g e he hg hs 0 k 0 (by simp)).1)

end Froehlich
