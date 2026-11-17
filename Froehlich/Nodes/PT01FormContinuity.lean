import Froehlich.Nodes.PT01FormRepresentative
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-! The actual cutoff residual form is operator-norm continuous, and
uniformly bounded on each bounded momentum set in the fixed graph norm. -/
noncomputable section
namespace Froehlich

theorem cutoffCommonFormOperator_continuous (n : ℕ) (e : ℝ) (p0 : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ)
    (Λ : GW.Operators.PositiveCutoff) :
    Continuous (fun p : GW.Space => cutoffCommonFormOperator n e p0 p hn he g Λ) := by
  let I := (HighEnergySpace (-p0) n).subtypeL
  let J := highEnergyEmbedding (-p0) n
  let A := formRepresentative (cutoffInteractionForm g Λ.val Λ.property (-p0))
  let c : ℂ := ((e-1+(n : ℝ) : ℝ) : ℂ)
  have hf : Continuous (fun p : GW.Space => fixedFreeFormOperator (-p0) (-p)+A) :=
    ((fixedFreeFormOperator_continuous (-p0)).comp continuous_neg).add continuous_const
  have hr : Continuous (fun p : GW.Space =>
      I.adjoint.comp ((fixedFreeFormOperator (-p0) (-p)+A).comp I)-c • (J.adjoint.comp J)) :=
    (continuous_const.clm_comp (hf.clm_comp continuous_const)).sub continuous_const
  convert hr using 1
  funext p
  exact cutoffCommonFormOperator_fixed_representative n e p0 p hn he g Λ

theorem cutoffCommonFormOperator_bounded_on (n : ℕ) (e : ℝ) (p0 : GW.Space)
    (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ)
    (Λ : GW.Operators.PositiveCutoff) (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ‖cutoffCommonFormOperator n e p0 p hn he g Λ‖ ≤ C := by
  have hcont := cutoffCommonFormOperator_continuous n e p0 hn he g Λ
  have hEndNorm : Continuous (fun T : HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n => ‖T‖) :=
    @continuous_norm (HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n)
      (ContinuousLinearMap.toSeminormedAddCommGroup (σ₁₂ := RingHom.id ℂ)
        (E := HighEnergySpace (-p0) n) (F := HighEnergySpace (-p0) n)).toSeminormedAddGroup
  have hnorm : Continuous (fun p : GW.Space => ‖cutoffCommonFormOperator n e p0 p hn he g Λ‖) :=
    hEndNorm.comp hcont
  have hb := (hK.isCompact_closure.image hnorm).isBounded
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  refine ⟨max C 0+1,by positivity,?_⟩
  intro p hp
  have hn : ‖cutoffCommonFormOperator n e p0 p hn he g Λ‖ ≤ C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (cutoffCommonFormOperator n e p0 p hn he g Λ).opNorm_nonneg]
      using hC _ ⟨p,subset_closure hp,rfl⟩
  exact hn.trans (by linarith [le_max_left C 0])

end Froehlich
