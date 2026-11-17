import Froehlich.Nodes.OP00KernelPairing
import Froehlich.Nodes.SY01Annihilation
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false

/-! Product-almost-everywhere Hermitian symmetry and actual conjugation. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (a : GW.Space → ℝ) (ha : MemLp a 2 volume) (ha0 : ∀ q, 0 ≤ a q)
  (k : GW.Space → GW.Space → ℂ) (hk : Measurable (Function.uncurry k))
  (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q r, ‖k q r‖ ≤ M*a q*a r)

theorem kernelIntegralOperator_adjoint
    (hsym : ∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
      k z.1 z.2 = (starRingEnd ℂ) (k z.2 z.1)) :
    (kernelIntegralOperator a ha ha0 k hk M hM hb).adjoint = kernelIntegralOperator a ha ha0 k hk M hM hb := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  calc
    _ = (starRingEnd ℂ) ⟪h,kernelIntegralOperator a ha ha0 k hk M hM hb f⟫_ℂ :=
      (inner_conj_symm _ _).symm
    _ = (starRingEnd ℂ) (∫ z : GW.Space × GW.Space, (starRingEnd ℂ) (h z.1)*(k z.1 z.2*f z.2)) := by
      rw [kernelIntegralOperator_inner a ha k hk M hb ha0 hM]
    _ = ∫ z : GW.Space × GW.Space, (starRingEnd ℂ) ((starRingEnd ℂ) (h z.1)*(k z.1 z.2*f z.2)) :=
      integral_conj.symm
    _ = ∫ z : GW.Space × GW.Space, (starRingEnd ℂ) ((starRingEnd ℂ) (h z.2)*(k z.2 z.1*f z.1)) :=
      (integral_prod_swap _).symm
    _ = ∫ z : GW.Space × GW.Space, (starRingEnd ℂ) (f z.1)*(k z.1 z.2*h z.2) := by
      apply integral_congr_ae
      filter_upwards [hsym] with z hz
      simp only [map_mul,starRingEnd_self_apply]
      rw [hz]
      ring
    _ = _ := (kernelIntegralOperator_inner a ha k hk M hb ha0 hM f h).symm

theorem kernelIntegralOperator_conjugation
    (hreal : ∀ᵐ z : GW.Space × GW.Space ∂((volume : Measure GW.Space).prod volume),
      (starRingEnd ℂ) (k z.1 z.2) = k z.1 z.2) (f : GW.OnePhonon) :
    kernelIntegralOperator a ha ha0 k hk M hM hb (conjugateOnePhonon f) =
      conjugateOnePhonon (kernelIntegralOperator a ha ha0 k hk M hM hb f) := by
  apply Lp.ext
  filter_upwards [kernelIntegralOperator_ae a ha ha0 k hk M hM hb (conjugateOnePhonon f),
    kernelIntegralOperator_ae a ha ha0 k hk M hM hb f,
    conjugateOnePhonon_ae (kernelIntegralOperator a ha ha0 k hk M hM hb f),
    Measure.ae_ae_of_ae_prod hreal] with q hc hf hconj hrow
  rw [hc,hconj,hf]
  unfold kernelRowIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjugateOnePhonon_ae f,hrow] with r hr hkr
  rw [hr,map_mul,hkr]

end Froehlich
