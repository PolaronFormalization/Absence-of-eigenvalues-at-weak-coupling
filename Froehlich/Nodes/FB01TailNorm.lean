import Froehlich.Nodes.FB01TailExtension
import GW.Operators.UniformFormLimit

/-! The uniform tail bound in the retained mixed form norm. -/
noncomputable section
namespace Froehlich

theorem cutoffInteraction_tail_norm (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ) (P : GW.Space) :
    ‖cutoffInteractionForm g Λ (hL.trans_le hLΛ) P - cutoffInteractionForm g L hL P‖ ≤
      lyHighConstant * |g| / Real.sqrt L := by
  let a := cutoffInteractionForm g Λ (hL.trans_le hLΛ) P - cutoffInteractionForm g L hL P
  have hC : 0 ≤ lyHighConstant * |g| / Real.sqrt L :=
    div_nonneg (mul_nonneg lyHighConstant_pos.le (abs_nonneg g)) (Real.sqrt_nonneg L)
  have hs (w u : EnergySpace P) : a w u = star (a u w) := by
    change cutoffInteractionForm g Λ (hL.trans_le hLΛ) P w u -
      cutoffInteractionForm g L hL P w u =
        star (cutoffInteractionForm g Λ (hL.trans_le hLΛ) P u w -
          cutoffInteractionForm g L hL P u w)
    exact (congrArg₂ (fun z t : ℂ => z-t)
      (cutoffInteractionForm_hermitian g Λ (hL.trans_le hLΛ) P w u)
      (cutoffInteractionForm_hermitian g L hL P w u)).trans (star_sub _ _).symm
  apply (GW.Analysis.form_norm_le_iff a hC).mpr
  exact GW.Operators.hermitian_mixed_bound (GW.Operators.boundedFormAlgebraic a) hs hC
    (lyHighForm_energy_diagonal_bound g L Λ hL hLΛ P)

end Froehlich
