import Froehlich.Nodes.OP00KernelNullset
import Froehlich.Nodes.OP00KernelSymmetries

set_option autoImplicit false

/-! OP00 / lem:dominatedkernel, on the actual GW one-particle space.
The fixed null set is arbitrary and the majorant constant has no sign premise. -/
noncomputable section
open MeasureTheory
namespace Froehlich

private theorem op00_global (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
    (ha0 : ∀ q, 0 ≤ a q) (k : GW.Space → GW.Space → ℂ)
    (hk : Measurable (Function.uncurry k)) (M : ℝ)
    (hb : ∀ q r, ‖k q r‖ ≤ M*a q*a r) :
    ∃ K : GW.OnePhonon →L[ℂ] GW.OnePhonon,
      ‖K‖ ≤ M*‖ha.toLp a‖^2 ∧
      (∀ f, K f =ᵐ[volume] kernelRowIntegral k f) ∧
      ((∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
        k z.1 z.2 = (starRingEnd ℂ) (k z.2 z.1)) → K.adjoint = K) ∧
      ((∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
        (starRingEnd ℂ) (k z.1 z.2) = k z.1 z.2) →
        ∀ f, K (conjugateOnePhonon f) = conjugateOnePhonon (K f)) := by
  have hbabs (q r : GW.Space) : ‖k q r‖ ≤ |M| * a q*a r :=
    (hb q r).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self M) (ha0 q)) (ha0 r))
  let K := kernelIntegralOperator a ha ha0 k hk |M| (abs_nonneg M) hbabs
  have hK : ‖K‖ ≤ |M| * ‖ha.toLp a‖^2 :=
    kernelIntegralOperator_norm_le a ha ha0 k hk |M| (abs_nonneg M) hbabs
  refine ⟨K,?_,kernelIntegralOperator_ae a ha ha0 k hk |M| (abs_nonneg M) hbabs,
    kernelIntegralOperator_adjoint a ha ha0 k hk |M| (abs_nonneg M) hbabs,
    kernelIntegralOperator_conjugation a ha ha0 k hk |M| (abs_nonneg M) hbabs⟩
  by_cases hM : 0 ≤ M
  · simpa only [abs_of_nonneg hM] using hK
  · have haZero := kernelNegativeMajorant_zero a k M (lt_of_not_ge hM) hb
    have hn : ‖ha.toLp a‖ = 0 := by
      have h := Lp.norm_toLp a ha
      simpa only [haZero,eLpNorm_zero,ENNReal.toReal_zero] using h
    simpa only [hn,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] using hK

theorem finalOP00 (a : GW.Space → ℝ) (ha : MemLp a 2 volume)
    (ha0 : ∀ q, 0 ≤ a q) (k : GW.Space → GW.Space → ℂ)
    (hk : Measurable (Function.uncurry k)) (M : ℝ)
    (N : Set GW.Space) (hN : volume N = 0)
    (hb : ∀ q ∉ N, ∀ r ∉ N, ‖k q r‖ ≤ M*a q*a r) :
    ∃ K : GW.OnePhonon →L[ℂ] GW.OnePhonon,
      ‖K‖ ≤ M*‖ha.toLp a‖^2 ∧
      (∀ f, K f =ᵐ[volume] kernelRowIntegral k f) ∧
      ((∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
        k z.1 z.2 = (starRingEnd ℂ) (k z.2 z.1)) → K.adjoint = K) ∧
      ((∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
        (starRingEnd ℂ) (k z.1 z.2) = k z.1 z.2) →
        ∀ f, K (conjugateOnePhonon f) = conjugateOnePhonon (K f)) := by
  classical
  obtain ⟨K,hK,hRow,hSym,hReal⟩ := op00_global (kernelCleanMajorant N a)
    (kernelCleanMajorant_memLp N hN a ha) (kernelCleanMajorant_nonnegative N a ha0)
    (kernelCleanKernel N k) (kernelCleanKernel_measurable N k hk) M (kernelCleanKernel_bound N a k M hb)
  refine ⟨K,?_,?_,?_,?_⟩
  · simpa only [kernelCleanMajorant_norm N hN a ha] using hK
  · intro f
    exact (hRow f).trans (kernelCleanKernel_row_ae N hN k f)
  · intro hs
    apply hSym
    filter_upwards [hs] with z hz
    by_cases hn : z.1 ∈ kernelNullHull N ∨ z.2 ∈ kernelNullHull N
    · have hn' : z.2 ∈ kernelNullHull N ∨ z.1 ∈ kernelNullHull N := hn.symm
      simp only [kernelCleanKernel,if_pos hn,if_pos hn',map_zero]
    · have hn' : ¬(z.2 ∈ kernelNullHull N ∨ z.1 ∈ kernelNullHull N) := fun h => hn h.symm
      simpa only [kernelCleanKernel,if_neg hn,if_neg hn'] using hz
  · intro hr
    apply hReal
    filter_upwards [hr] with z hz
    unfold kernelCleanKernel
    split_ifs
    · exact map_zero _
    · exact hz

end Froehlich
