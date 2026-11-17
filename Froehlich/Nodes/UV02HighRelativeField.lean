import Froehlich.Nodes.UV02RelativeField
import Froehlich.Nodes.UV02HighFreeInverse
import Froehlich.Nodes.UV02FreeGraph
import Froehlich.Nodes.BA02

/-! The source projected field and Neumann factor on every actual closed
high sector, including n=0. The same fixed-cutoff shift estimate applies. -/
noncomputable section
namespace Froehlich

def highShiftRelativeField (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (f : GW.OnePhonon) :
    HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  (highSectorProject n).comp ((fieldRestriction f).comp
    ((freeShiftNumberInverse P c hc).comp (HighSectorSpace n).subtypeL))

theorem highShiftRelativeField_norm_le (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (f : GW.OnePhonon) :
    ‖highShiftRelativeField P c hc n f‖ ≤ 2*‖f‖*(Real.sqrt c)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖highSectorProjection n (fieldRestriction f (freeShiftNumberInverse P c hc (u : GW.Fock.Carrier)))‖ ≤ _
  calc
    _ ≤ ‖fieldRestriction f (freeShiftNumberInverse P c hc (u : GW.Fock.Carrier))‖ := highSectorProjection_norm_le n _
    _ ≤ 2*‖f‖*‖freeShiftNumberInverse P c hc (u : GW.Fock.Carrier)‖ := fieldRestriction_bound f _
    _ ≤ 2*‖f‖*((Real.sqrt c)⁻¹*‖u‖) := mul_le_mul_of_nonneg_left
      (freeShiftNumberInverse_norm_le P c hc u) (by positivity)
    _ = _ := by ring

theorem highCutoffField_shift_exists (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (b : ℝ) :
    ∃ c : ℝ, ∃ hc : 1 ≤ c, b<c ∧
      ‖highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property)‖<1/2 := by
  obtain ⟨c,hc,hb,hsmall⟩ := finiteField_shift_choice (cutoffFormFactorL2 g Λ.val Λ.property) b
  exact ⟨c,hc,hb,(highShiftRelativeField_norm_le P c hc n _).trans_lt hsmall⟩

variable (g : ℝ) (P : GW.Space) (n : ℕ) (Λ : GW.Operators.PositiveCutoff) (c : ℝ) (hc : 1 ≤ c)

def highCutoffShiftFactorInverse : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  neumannInverse (-(highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property)))

def highCutoffShiftSolution (z : HighSectorSpace n) : HighSectorSpace n :=
  freeShiftHighInverse P c hc n (highCutoffShiftFactorInverse g P n Λ c hc z)

theorem highCutoffShiftSolution_mem_free (z : HighSectorSpace n) :
    (highCutoffShiftSolution g P n Λ c hc z : GW.Fock.Carrier) ∈ (freeFiberOperator P).domain :=
  freeShiftInverse_mem_free_domain P c hc _

include hc in
theorem highCutoffShiftFactorInverse_right
    (hsmall : ‖highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property)‖<1/2) :
    (1+highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property))*
      highCutoffShiftFactorInverse g P n Λ c hc=1 := by
  have hn : ‖-(highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property))‖<1 :=
    (ContinuousLinearMap.opNorm_neg _).trans_lt (hsmall.trans (by norm_num))
  simpa only [highCutoffShiftFactorInverse,sub_neg_eq_add] using
    neumannInverse_right (-(highShiftRelativeField P c hc n (cutoffFormFactorL2 g Λ.val Λ.property))) hn

end Froehlich
