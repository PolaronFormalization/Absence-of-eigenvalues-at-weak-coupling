import Froehlich.Nodes.PT01ResidualTests
import Froehlich.Nodes.PT01ResidualData
import Froehlich.Nodes.PT01CoreWeakInverseField
import Froehlich.Nodes.PT01InverseFieldLimit

set_option autoImplicit false

/-! The actual finite-cutoff pull-through identity in local physical L2.
All residual construction data are discharged by the actual form family. -/
noncomputable section
open MeasureTheory
namespace Froehlich

variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def cutoffPullthroughSource (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K) :=
  localPullthroughSource m K F
    (cutoffPullthroughVector m e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩)
    (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
    ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)

include R hR hKR in
theorem cutoffPullthrough_local_of_data
    (hT : AEStronglyMeasurable
      (fun k : GW.Space => (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m)) ((volume : Measure GW.Space).restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ‖ ≤ M)
    (F : NumberFormSpace) (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩))) =
      (HighSectorSpace m).subtypeL.compLp
        (localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Λ
          (cutoffPullthroughSource m e p he Λ g hg hs K F hF)) := by
  let U := cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR ⟨numberFormEmbedding F,hF⟩
  let S := cutoffPullthroughSource m e p he Λ g hg hs K F hF
  let G := localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Λ S
  have hEq : ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
        HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m) (U k) =
        (highEnergyEmbedding 0 m).adjoint (S k) := by
    have hd := (highEnergyEmbedding 0 m).adjoint.coeFn_compLp S
    filter_upwards [cutoffEnergyResidual_weak_ae m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF,hd]
      with k hweak hdual
    change cutoffLocalDualSource m e p he Λ g hg hs K F hF k =
      (highEnergyEmbedding 0 m).adjoint (S k) at hdual
    exact hweak.trans hdual
  have hinvert : ∀ (U1 : Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K))
      (S1 G1 : Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K)),
      (∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
        (cutoffCommonFormOperator m e 0 (p+k) ((Nat.le_succ m).trans hm) he g Λ :
          HighEnergySpace 0 m →L[ℂ] HighEnergySpace 0 m) (U1 k) =
          (highEnergyEmbedding 0 m).adjoint (S1 k)) →
      (G1 =ᵐ[(volume : Measure GW.Space).restrict K]
        (fun k => cutoffAuxiliaryResolvent m e (p+k) he Λ g hg hs (S1 k))) →
      (highEnergyEmbedding 0 m).compLp U1 = G1 := by
    simpa only [neg_zero] using! cutoff_fixedWeakField_Lp m e 0
      ((Nat.le_succ m).trans hm) he g hg hs Λ K (fun k : GW.Space => p+k)
  have hUG : (highEnergyEmbedding 0 m).compLp U = G :=
    hinvert U S G hEq (localCutoffInverseField_ae m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Λ S)
  let I := (HighSectorSpace m).subtypeL
  have hleft : LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩))) =
        I.compLp ((highEnergyEmbedding 0 m).compLp U) := by
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ K
        (annihilationField (freeGraphNumberCoordinates (-p)
          (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩))),
      I.coeFn_compLp ((highEnergyEmbedding 0 m).compLp U),
      (highEnergyEmbedding 0 m).coeFn_compLp U,
      cutoffAuxiliaryLocalEnergyField_physical m e p hm he Λ g hg hs K hK R hR hKR
        ⟨numberFormEmbedding F,hF⟩] with k hr hi hj hu
    rw [hi,hj]
    exact hr.trans hu.symm
  rw [hUG] at hleft
  exact hleft

include R hR hKR in
theorem cutoffPullthrough_local (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) :
    LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K
      (annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩))) =
      (HighSectorSpace m).subtypeL.compLp
        (localCutoffInverseField m e p ((Nat.le_succ m).trans hm) he g hg hs K hK Λ
          (cutoffPullthroughSource m e p he Λ g hg hs K F hF)) := by
  obtain ⟨M,_,hT,hM⟩ := cutoffResidualFormData m e p ((Nat.le_succ m).trans hm) he g Λ K hK R hKR
  exact cutoffPullthrough_local_of_data m e p hm he Λ g hg hs K hK R hR hKR hT M hM F hF

end Froehlich
