import Froehlich.Nodes.PT01CutoffGraph
import Froehlich.Nodes.PT01SourceField
import Froehlich.Nodes.FC08
import Froehlich.Nodes.FC07ProjectedCore

set_option autoImplicit false

/-! The genuine local energy-valued residual at a fixed cutoff. The form
family is the actual compressed shifted form; measurability and norm-bound
arguments are its construction data, not a residual equation. -/
noncomputable section
open MeasureTheory
namespace Froehlich

variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffPullthroughVector (f : HighSectorSpace (m+1)) : HighSectorSpace m :=
  ⟨(cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs f : GW.Fock.Carrier),
    highSector_mem_of_succ m _ (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs f).property⟩

variable (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def cutoffLocalDualSource (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  localPullthroughDualSource m K F
    (cutoffPullthroughVector m e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩)
    (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
    ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)

variable (hT : AEStronglyMeasurable
    (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ : HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m))
    ((volume : Measure GW.Space).restrict K)) (M : ℝ)
    (hM : ∀ k ∈ K, ‖cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ‖ ≤ M)

def cutoffEnergyResidual (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  operatorFieldValue (V := HighEnergySpace 0 m) (W := HighEnergySpace 0 m) K hK
    (fun k => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ : HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) hT M hM
    (cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩) -
      cutoffLocalDualSource m e p he Λ g hg hs K F hF

theorem cutoffEnergyResidual_ae (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      cutoffEnergyResidual m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF k =
        @Sub.sub (HighEnergySpace 0 m) inferInstance
          ((cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
            HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)
            (cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩ k))
          (cutoffLocalDualSource m e p he Λ g hg hs K F hF k) := by
  let U := cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩
  let B := operatorFieldValue (V := HighEnergySpace 0 m) (W := HighEnergySpace 0 m) K hK
    (fun k => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ : HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) hT M hM U
  let D := cutoffLocalDualSource m e p he Λ g hg hs K F hF
  filter_upwards [Lp.coeFn_sub B D,operatorFieldValue_ae (V := HighEnergySpace 0 m) (W := HighEnergySpace 0 m) K hK _ hT M hM U] with k hsub hval
  simp only [Pi.sub_apply] at hsub
  change (B-D) k = _
  rw [hsub,hval]
  rfl

end Froehlich
