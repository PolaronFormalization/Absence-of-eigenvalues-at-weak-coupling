import Froehlich.Nodes.PT01ResidualSourcePairing
import Froehlich.Nodes.PT01CoreLimitIdentity
import Froehlich.Nodes.FC09

set_option autoImplicit false

/-! The actual finite-cutoff energy residual vanishes. Only the proved
free-graph tested identity and legitimate NumberForm source pairing enter. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (hT : AEStronglyMeasurable
      (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) ((volume : Measure GW.Space).restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ‖ ≤ M)
    (F : NumberFormSpace) (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1))

theorem cutoffEnergyResidual_test_zero (w : highEnergyTestCore 0 m)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    localL2TestFunctional K chi w.val
      (cutoffEnergyResidual m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF) = 0 := by
  let x := cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩
  have hx : graphEmbedding (-p) x ∈ HighSectorSpace (m+1) := by
    rw [cutoffAuxiliaryGraphCoordinate_physical]
    exact (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩).property
  let B : Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
    operatorFieldValue (V := HighEnergySpace 0 m) (W := HighEnergySpace 0 m) K hK
      (fun k => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) hT M hM
      (cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩)
  let D := cutoffLocalDualSource m e p he Λ g hg hs K F hF
  have hleft : localL2TestFunctional K chi w.val B =
      cutoffGraphTestRHS g (-p) (m+1) Λ e K hK chi (ptCorePhysicalTest m w) x :=
    cutoff_freeGraph_test_identity p m e hm he g Λ K hK R hR hKR hT M hM x hx w chi
  have hright : localL2TestFunctional K chi w.val D =
      cutoffGraphTestRHS g (-p) (m+1) Λ e K hK chi (ptCorePhysicalTest m w) x :=
    cutoffLocalDualSource_test m e p hm he Λ g hg hs K hK F hF w chi
  change localL2TestFunctional K chi w.val (B-D) = 0
  rw [map_sub,hleft,hright,sub_self]

theorem cutoffEnergyResidual_zero :
    cutoffEnergyResidual m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF = 0 := by
  apply residual_zero_of_dense_scalar_tests ((volume : Measure GW.Space).restrict K) _
    (highEnergyTestCore 0 m) (highEnergyTestCore_dense 0 m)
  intro w hw chi
  have h := cutoffEnergyResidual_test_zero m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF ⟨w,hw⟩ chi
  rw [localL2TestFunctional_integral] at h
  exact h

include hT M hM in
theorem cutoffEnergyResidual_weak_ae :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)
        (cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩ k) =
        cutoffLocalDualSource m e p he Λ g hg hs K F hF k := by
  have hz := Lp.eq_zero_iff_ae_eq_zero.mp
    (cutoffEnergyResidual_zero m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF)
  filter_upwards [cutoffEnergyResidual_ae m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF,hz]
    with k hval hzero
  have heq := hval.symm.trans hzero
  exact sub_eq_zero.mp heq

end Froehlich
