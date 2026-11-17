import Froehlich.Nodes.FC07ProjectedCore
import Froehlich.Nodes.FC03
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Complex scalar tests of genuine annihilation fields. In the core use,
the input Lu is again a core vector, so FC03 smearing is legitimate. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem smearedCreation_test_integral (chi : GW.OnePhonon) (w z : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪numberFormEmbedding w,annihilationField z k⟫_ℂ) volume ∧
    (∫ k, (starRingEnd ℂ) (chi k)*⟪numberFormEmbedding w,annihilationField z k⟫_ℂ)=
      ⟪creationRestriction chi w,numberFormEmbedding z⟫_ℂ := by
  let L := innerSL ℂ (numberFormEmbedding w)
  have hv := smeared_annihilation_integrable chi z
  have hi := L.integrable_comp hv
  change Integrable (fun k => ⟪numberFormEmbedding w,(starRingEnd ℂ) (chi k) • annihilationField z k⟫_ℂ) volume at hi
  have hs : Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪numberFormEmbedding w,annihilationField z k⟫_ℂ) volume := by
    simpa only [inner_smul_right] using hi
  refine ⟨hs,?_⟩
  calc
    _ = ∫ k, L ((starRingEnd ℂ) (chi k) • annihilationField z k) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun k => (inner_smul_right _ _ _).symm)
    _ = L (∫ k, (starRingEnd ℂ) (chi k) • annihilationField z k) := L.integral_comp_comm hv
    _ = ⟪numberFormEmbedding w,annihilationRestriction chi z⟫_ℂ := by
      rw [←smeared_annihilation_integral chi z]
      rfl
    _ = _ := (smeared_adjoint_pairing chi w z).symm

theorem projectedCutoffCore_output_test (g : ℝ) (P : GW.Space) (n : ℕ)
    (Lambda : GW.Operators.PositiveCutoff) (e : ℝ) (u w : boundedMomentumCore) (chi : GW.OnePhonon) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),
      annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Lambda e u)) k⟫_ℂ) volume ∧
    (∫ k, (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),
      annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Lambda e u)) k⟫_ℂ)=
      ⟪creationRestriction chi (coreNumberLift w),
        (coreProjectedCutoffShiftAction g P n Lambda e u : GW.Fock.Carrier)⟫_ℂ := by
  simpa only [coreNumberLift_embedding] using
    smearedCreation_test_integral chi (coreNumberLift w)
      (coreNumberLift (coreProjectedCutoffShiftAction g P n Lambda e u))

end Froehlich
