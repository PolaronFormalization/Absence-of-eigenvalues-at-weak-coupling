import Froehlich.Nodes.PT01Residual
import Froehlich.Nodes.PT01CoreLocalAdjoint
import Froehlich.Nodes.PT01CoreFormTesting
import Froehlich.Nodes.PT01CoreLimit
import Froehlich.Nodes.PT01GraphActionSource

set_option autoImplicit false

/-! The actual local dual source equals the physical graph-limit RHS when
tested by any complex local scalar test and genuine high-energy core test. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffLocalDualSource_test (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (K : Set GW.Space) (hK : MeasurableSet K) (F : NumberFormSpace)
    (hF : numberFormEmbedding F ∈ HighSectorSpace (m+1)) (w : highEnergyTestCore 0 m)
    (chi : Lp ℂ 2 (volume.restrict K)) :
    localL2TestFunctional K chi w.val (cutoffLocalDualSource m e p he Λ g hg hs K F hF) =
      cutoffGraphTestRHS g (-p) (m+1) Λ e K hK chi (ptCorePhysicalTest m w)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩) := by
  let W := ptCorePhysicalTest m w
  let WN := coreNumberLift W
  let U := cutoffPullthroughVector m e p he Λ g hg hs ⟨numberFormEmbedding F,hF⟩
  let x := cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs ⟨numberFormEmbedding F,hF⟩
  let c : ℂ := ⟪(W : GW.Fock.Carrier),(U : GW.Fock.Carrier)⟫_ℂ
  have hW : numberFormEmbedding WN = (W : GW.Fock.Carrier) := coreNumberLift_embedding W
  have hCreate := localCreation_source_test K hK chi WN F
  have hfirst : Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪(W : GW.Fock.Carrier),annihilationField F k⟫_ℂ) (volume.restrict K) := by
    simpa only [hW] using hCreate.1
  have htailG : Integrable (fun k => ((starRingEnd ℂ) (localScalarTestExtension K hK chi k)*
      cutoffFormFactorL2 g Λ.val Λ.property k)*c) volume := by
    simpa only [RCLike.inner_apply'] using
      (L2.integrable_inner (𝕜 := ℂ) (localScalarTestExtension K hK chi)
        (cutoffFormFactorL2 g Λ.val Λ.property)).mul_const c
  have htailAE : (fun k => ((starRingEnd ℂ) (localScalarTestExtension K hK chi k)*
      cutoffFormFactorL2 g Λ.val Λ.property k)*c) =ᵐ[volume.restrict K]
      (fun k => ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Λ.val Λ.property k)*c) := by
    filter_upwards [localScalarTestExtension_restrict_ae K hK chi] with k hk
    rw [hk]
  have htail : Integrable (fun k => ((starRingEnd ℂ) (chi k)*
      cutoffFormFactorL2 g Λ.val Λ.property k)*c) (volume.restrict K) :=
    htailG.restrict.congr htailAE
  have hRHS : cutoffGraphTestRHS g (-p) (m+1) Λ e K hK chi W x =
      ⟪creationRestriction (localScalarTestExtension K hK chi) WN,numberFormEmbedding F⟫_ℂ -
        ∫ k in K, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Λ.val Λ.property k)*c := by
    change ⟪creationRestriction (localScalarTestExtension K hK chi) WN,
      cutoffShiftFreeGraphAction g (-p) (m+1) Λ e x⟫_ℂ -
      (∫ k in K, (starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Λ.val Λ.property k)*
        ⟪(W : GW.Fock.Carrier),graphEmbedding (-p) x⟫_ℂ = _
    rw [cutoffShiftFreeGraphAction_resolvent,cutoffAuxiliaryGraphCoordinate_physical,integral_mul_const]
    rfl
  rw [hRHS,localL2TestFunctional_integral]
  have hp := localPullthroughDualSource_pairing m K F hF U
    (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
    ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K)
  calc
    _ = ∫ k in K, ((starRingEnd ℂ) (chi k)*⟪(W : GW.Fock.Carrier),annihilationField F k⟫_ℂ -
        ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Λ.val Λ.property k)*c) := by
      apply integral_congr_ae
      filter_upwards [hp] with k hk
      change (starRingEnd ℂ) (chi k)*⟪w.val,
        localPullthroughDualSource m K F U (fun k => cutoffFormFactorL2 g Λ.val Λ.property k)
          ((Lp.memLp (cutoffFormFactorL2 g Λ.val Λ.property)).restrict K) k⟫_ℂ = _
      rw [hk w.val,inner_sub_right,inner_smul_right]
      change (starRingEnd ℂ) (chi k)*(⟪(W : GW.Fock.Carrier),annihilationField F k⟫_ℂ -
        cutoffFormFactorL2 g Λ.val Λ.property k*c) = _
      ring
    _ = _ := by
      rw [integral_sub hfirst htail]
      rw [←hW]
      rw [hCreate.2]

end Froehlich
