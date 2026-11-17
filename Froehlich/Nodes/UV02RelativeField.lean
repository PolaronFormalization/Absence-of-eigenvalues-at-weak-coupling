import Froehlich.Nodes.UV02NumberInverse
import Froehlich.Nodes.FB01Forms
import Froehlich.Nodes.GW06

/-! At each fixed finite cutoff, the actual field times the free shifted
inverse is bounded and becomes small by choosing the source shift c. -/
noncomputable section
namespace Froehlich

def freeShiftRelativeField (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (f : GW.OnePhonon) :
    GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  (fieldRestriction f).comp (freeShiftNumberInverse P c hc)

theorem freeShiftRelativeField_norm_le (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (f : GW.OnePhonon) :
    ‖freeShiftRelativeField P c hc f‖ ≤ 2*‖f‖*(Real.sqrt c)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖fieldRestriction f (freeShiftNumberInverse P c hc u)‖ ≤ _
  calc
    _ ≤ 2*‖f‖*‖freeShiftNumberInverse P c hc u‖ := fieldRestriction_bound f _
    _ ≤ 2*‖f‖*((Real.sqrt c)⁻¹*‖u‖) := mul_le_mul_of_nonneg_left
      (freeShiftNumberInverse_norm_le P c hc u) (by positivity)
    _ = _ := by ring

theorem finiteField_shift_choice (f : GW.OnePhonon) (b : ℝ) :
    ∃ c : ℝ, 1 ≤ c ∧ b<c ∧ 2*‖f‖*(Real.sqrt c)⁻¹<1/2 := by
  let c := (4*‖f‖+1)^2+|b|+1
  have hc : 1 ≤ c := by dsimp only [c]; nlinarith [sq_nonneg (4*‖f‖+1),abs_nonneg b]
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hb : b<c := by
    have hab : b ≤ |b| := le_abs_self b
    dsimp only [c]
    nlinarith [sq_nonneg (4*‖f‖+1)]
  have hroot : 4*‖f‖+1 ≤ Real.sqrt c :=
    Real.le_sqrt_of_sq_le (by dsimp only [c]; nlinarith [abs_nonneg b])
  refine ⟨c,hc,hb,?_⟩
  rw [←div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr hcpos)).mpr
  nlinarith [norm_nonneg f]

theorem cutoffField_neumann_shift_exists (g : ℝ) (P : GW.Space)
    (Λ : GW.Operators.PositiveCutoff) (b : ℝ) :
    ∃ c : ℝ, ∃ hc : 1 ≤ c, b<c ∧
      ‖freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property)‖<1/2 := by
  obtain ⟨c,hc,hb,hsmall⟩ := finiteField_shift_choice (cutoffFormFactorL2 g Λ.val Λ.property) b
  exact ⟨c,hc,hb,(freeShiftRelativeField_norm_le P c hc _).trans_lt hsmall⟩

end Froehlich
