import Froehlich.Nodes.PT01CoreTesting

/-! Testing the actual projected cutoff core field against a complex L²
scalar test. Only legitimate core outputs are annihilated on the right. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem projectedCutoffCore_field_test (g : ℝ) (P : GW.Space) (n : ℕ)
    (Lambda : GW.Operators.PositiveCutoff) (e : ℝ) (u w : boundedMomentumCore) (chi : GW.OnePhonon) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ) volume ∧
    (∫ k, (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ)=
      ⟪creationRestriction chi (coreNumberLift w),
        (coreProjectedCutoffShiftAction g P n Lambda e u : GW.Fock.Carrier)⟫_ℂ -
      ∫ k, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ := by
  obtain ⟨hfirst,hfirstEq⟩ := projectedCutoffCore_output_test g P n Lambda e u w chi
  have htail : Integrable (fun k => ((starRingEnd ℂ) (chi k)*
      cutoffFormFactorL2 g Lambda.val Lambda.property k)*
      ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) volume := by
    simpa only [RCLike.inner_apply'] using
      (L2.integrable_inner (𝕜 := ℂ) chi (cutoffFormFactorL2 g Lambda.val Lambda.property)).mul_const
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ
  have he : (fun k => (starRingEnd ℂ) (chi k)*
      ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ) =ᵐ[volume]
      (fun k => (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),
        annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Lambda e u)) k⟫_ℂ -
        ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
          ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) := by
    filter_upwards [projectedCutoffShiftField_ae g P n Lambda e u] with k hk
    rw [hk,inner_sub_right,inner_smul_right]
    ring
  refine ⟨(hfirst.sub htail).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_sub hfirst htail,hfirstEq]

end Froehlich
